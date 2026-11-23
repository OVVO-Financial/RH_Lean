import RHLean.Geometry.NativeCMSerreGenericPoints
import RHLean.Geometry.NativeCMSerreMixedPeriods

/-!
# The native coefficient-period image on actual generic scheme points

The existing one-coordinate native lattice is identified with the literal
inverse-half-different by its already proved coordinate equivalence. Its
original pure CM-type exponential is then carried to the actual
represented scheme points. The exact integral period image and the full
O_E action are retained. No free replacement of the coefficient ideal is
used, and no assertion about a mixed signature is made from this one
pure factor.

This is native glue of the already attributed period and scheme tensor
constructors; no further external declarations are imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical TensorProduct Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM EllipticSeed
open SerreScheme SchemeTheory SchemeTheory.WeierstrassCurve Weierstrass

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E)
    (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))

/-- The singleton coordinate map retains the original product-span
lattice and the original coefficient ideal. -/
omit [IsCMField H.E] in
def coefficientTwistedOne :
    twistedLattice H B 1 ≃ₗ[𝓞 H.E] (coefficientIdeal H B : Submodule (𝓞 H.E) H.E) :=
  (twistedCoordinates H B 1).trans
    (LinearEquiv.funUnique (Fin 1) (𝓞 H.E)
      (coefficientIdeal H B : Submodule (𝓞 H.E) H.E))

variable (τ₀ : cmTypeFinset H)
    {F : Type} [Field F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G (τ₀ : H.E →+* ℂ) C))
    (a : OAct (OK G) (schemeOver V))
    (hact : ∀ c : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C) z)) ≫ a.act c =
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C)
          (embed G (τ₀ : H.E →+* ℂ) c * z))))

def coefficientGenericPointEquiv :
    twistedLattice H B 1 ⊗[OK G] Torus G (τ₀ : H.E →+* ℂ) ≃ₗ[OK G]
      Pts (coefficientSerreSchemeAct H G hbar B hB 1 a) (specOver F ℂ) :=
  (((coefficientTwistedOne H B).restrictScalars (OK G)).rTensor
    (Torus G (τ₀ : H.E →+* ℂ))).trans
      ((coefficientSerreFrame H G hbar B hB 1).genericPointEquiv
        (τ₀ : H.E →+* ℂ) V C hVC a hact)

theorem coefficientGenericPointEquiv_coefficient (c : 𝓞 H.E)
    (t : twistedLattice H B 1 ⊗[OK G] Torus G (τ₀ : H.E →+* ℂ)) :
    Pts.hom (coefficientGenericPointEquiv H G hbar B hB τ₀ V C hVC a hact (c • t)) =
      Pts.hom (coefficientGenericPointEquiv H G hbar B hB τ₀ V C hVC a hact t) ≫
        (coefficientSerreSchemeFullAction H G hbar B hB 1 a).act c := by
  have he :
      (((coefficientTwistedOne H B).restrictScalars (OK G)).rTensor
        (Torus G (τ₀ : H.E →+* ℂ))) (c • t) =
      c • (((coefficientTwistedOne H B).restrictScalars (OK G)).rTensor
        (Torus G (τ₀ : H.E →+* ℂ))) t := by
    induction t using TensorProduct.inductionOn with
    | tmul m z =>
      simp only [← TensorProduct.smul_tmul', LinearEquiv.rTensor_tmul]
      exact congrArg (fun m => m ⊗ₜ[OK G] z) (map_smul (coefficientTwistedOne H B) c m)
    | add t u ht hu => simp only [smul_add, map_add, ht, hu]
  change Pts.hom ((coefficientSerreFrame H G hbar B hB 1).genericPointEquiv
      (τ₀ : H.E →+* ℂ) V C hVC a hact _) = _
  rw [he]
  exact TraceFrame.genericPointEquiv_coefficient _ _ _ _ _ _ _ _ _

variable [Algebra (OK G) ℂ]
    (hcompat : ∀ τ : cmTypeFinset H,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ)

def coefficientGenericPeriodExponential :
    (cmTypeFinset H → Fin 1 → ℂ) →ₗ[OK G]
      Pts (coefficientSerreSchemeAct H G hbar B hB 1 a) (specOver F ℂ) :=
  (coefficientGenericPointEquiv H G hbar B hB τ₀ V C hVC a hact).toLinearMap.comp
    (pureSerreExponential H G hcompat B hB 1 τ₀)

theorem coefficientGenericPeriodExponential_surjective :
    Function.Surjective
      (coefficientGenericPeriodExponential H G hbar B hB τ₀ V C hVC a hact hcompat) :=
  (coefficientGenericPointEquiv H G hbar B hB τ₀ V C hVC a hact).surjective.comp
    (pureSerreExponential_surjective H G hcompat B hB 1 τ₀)

/-- The period image is the original integral native image, including
its original index. The parameter is the original period, not u⁻¹ times it. -/
theorem coefficientGenericPeriodExponential_ker (v : cmTypeFinset H → Fin 1 → ℂ) :
    coefficientGenericPeriodExponential H G hbar B hB τ₀ V C hVC a hact hcompat v = 0 ↔
      v ∈ (purePeriodLinear H G hcompat B 1).range := by
  change coefficientGenericPointEquiv H G hbar B hB τ₀ V C hVC a hact
    (pureSerreExponential H G hcompat B hB 1 τ₀ v) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, pureSerreExponential_ker]

theorem coefficientGenericPeriodExponential_coefficient (c : 𝓞 H.E)
    (v : cmTypeFinset H → Fin 1 → ℂ) :
    Pts.hom (coefficientGenericPeriodExponential H G hbar B hB τ₀ V C hVC a hact hcompat
      (rawCoefficientAction H 1 c v)) =
      Pts.hom (coefficientGenericPeriodExponential H G hbar B hB τ₀ V C hVC a hact hcompat v) ≫
        (coefficientSerreSchemeFullAction H G hbar B hB 1 a).act c := by
  change Pts.hom (coefficientGenericPointEquiv H G hbar B hB τ₀ V C hVC a hact
      (pureSerreExponential H G hcompat B hB 1 τ₀ (rawCoefficientAction H 1 c v))) = _
  rw [pureSerreExponential_coefficient]
  exact coefficientGenericPointEquiv_coefficient H G hbar B hB τ₀ V C hVC a hact c _

/-- The original period tensor has the actual normalized-model point,
with the same nontrivial inverse u factor and the same coefficient map. -/
theorem coefficientGenericPeriodExponential_period_smul
    (z : ℂ) (x : twistedLattice H B 1) :
    Pts.hom (coefficientGenericPeriodExponential H G hbar B hB τ₀ V C hVC a hact hcompat
      (z • purePeriodLinear H G hcompat B 1 x)) =
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C) ((C.u : ℂ)⁻¹ * z))) ≫
          (coefficientSerreSchemeTensor H G hbar B hB 1 a).tmul
            (coefficientTwistedOne H B x) := by
  change Pts.hom (coefficientGenericPointEquiv H G hbar B hB τ₀ V C hVC a hact
    (pureSerreExponential H G hcompat B hB 1 τ₀
      (z • purePeriodLinear H G hcompat B 1 x))) = _
  rw [pureSerreExponential_period_smul]
  change Pts.hom ((coefficientSerreFrame H G hbar B hB 1).genericPointEquiv
    (τ₀ : H.E →+* ℂ) V C hVC a hact
    ((((coefficientTwistedOne H B).restrictScalars (OK G)).rTensor
      (Torus G (τ₀ : H.E →+* ℂ)))
      (x ⊗ₜ[OK G] QuotientAddGroup.mk' (period G (τ₀ : H.E →+* ℂ)).range z))) = _
  rw [LinearEquiv.rTensor_tmul, TraceFrame.genericPointEquiv_tmul]

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
