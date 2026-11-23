import RHLean.Geometry.NativeCMSerreGenericPeriod
import RHLean.Geometry.NativeCMSerreSchemeGeometry
import RHLean.Geometry.NativeCMSerreBundleSymmetry
import RHLean.Geometry.NativeCMWeierstrassPolarizedSeed

/-!
# One actual generic Serre seed on the native inverse half-different

The half-different is chosen once. The integral polarized elliptic seed
is then chosen once, and the genuine quadratic-order scheme action is
constructed on its specified normalized generic fibre over a finite
number field. The original trace frame represents the tensor on the
literal coefficient ideal. Its geometry, signed origin bundle, exact
original periods and full CM coefficient action are proved together.

This is a native join of the attributed constructions imported above.
The tensor bundle is proved rigidified and symmetric here. Ampleness,
the integral extension of the order action, and the arithmetic Lie and
class-group mean identifications are not conclusions of this theorem.
The displayed seed is one pure CM factor; it is not a replacement for
the separate positive and negative factors of a mixed signature.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical TensorProduct Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM NativeRawHostPolarization
open EllipticSeed SerreScheme SchemeTheory SchemeTheory.WeierstrassCurve
open SchemeTheory.WeierstrassLie Weierstrass WeierstrassTangent

/-- The actual native projective tensor, its specified generic seed and
its original periods are constructed on one set of witnesses. -/
theorem nativeDyadicHost_exists_genericSerreSeed
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let hbar := nativeDyadicGeometricHost_bar_eq e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ τ₀ : cmTypeFinset H.toHostRaw,
        let _ : Algebra (OK G) ℂ := (embed G (τ₀ : H.E →+* ℂ)).toAlgebra
        ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
          (W : _root_.WeierstrassCurve (𝓞 M)) (w : 𝓞 M)
          (C : _root_.WeierstrassCurve.VariableChange ℂ) (hΔ : W.Δ = 1),
          let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
          (∀ x : H.E, (τ₀ : H.E →+* ℂ) x ∈ M) ∧
          ((w : M) : ℂ) = omega G (τ₀ : H.E →+* ℂ) ∧
          IsLieBasis ![integralVector W] ∧ (originLB W).IsLB ∧
          (Rigidified (schemeOver W) (originLB W) ∧
            Sym (schemeOver W) (originLB W) ∧
            RelAmple (schemeOver W) (originLB W) ∧
            KTriv (schemeOver W) (originLB W)) ∧
          (C.u : ℂ) ^ 12 * (latticeCurve (periodPair G (τ₀ : H.E →+* ℂ))).Δ = 1 ∧
          ∃ hC : C • W.baseChange ℂ = latticeCurve (periodPair G (τ₀ : H.E →+* ℂ)),
            Function.Surjective (schemeExponential G (τ₀ : H.E →+* ℂ) W C hC) ∧
            (∀ z, schemeExponential G (τ₀ : H.E →+* ℂ) W C hC z = 0 ↔
              z ∈ lattice G (τ₀ : H.E →+* ℂ)) ∧
            HasDerivAt (originZ (periodPair G (τ₀ : H.E →+* ℂ)) C) (C.u : ℂ)⁻¹ 0 ∧
            ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
              (V : _root_.WeierstrassCurve F) (_ : V.IsElliptic)
              (hVC : V.baseChange ℂ = latticeCurve
                (rescaledPeriods G (τ₀ : H.E →+* ℂ) C))
              (a : OAct (OK G) (schemeOver V)),
              let A := coefficientSerreScheme H.toHostRaw G hbar B hB 1 a
              let N := coefficientSerreOriginBundle H.toHostRaw G hbar B hB 1 V a
              V = shortModel ((W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom) ∧
              (∀ c : OK G, ∀ z : ℂ,
                ofAffinePoint V ℂ ((pointCongr hVC).symm
                  (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C) z)) ≫ a.act c =
                ofAffinePoint V ℂ ((pointCongr hVC).symm
                  (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C)
                    (embed G (τ₀ : H.E →+* ℂ) c * z)))) ∧
              Smooth A.hom ∧ IsProper A.hom ∧ GeometricallyConnected A.hom ∧
              N.IsLB ∧ Rigidified A N ∧ Sym A N ∧
              Module.finrank ℂ (ℂ ⊗[OK G] coefficientIdeal H.toHostRaw B) = 2 * 2 ^ e ∧
              ∃ P : twistedLattice H.toHostRaw B 1 →ₗ[OK G]
                  (cmTypeFinset H.toHostRaw → Fin 1 → ℂ),
                ∃ ex : (cmTypeFinset H.toHostRaw → Fin 1 → ℂ) →ₗ[OK G]
                    Pts (coefficientSerreSchemeAct H.toHostRaw G hbar B hB 1 a) (specOver F ℂ),
                  (∀ x τ i, P x τ i = (τ : H.E →+* ℂ) (x.1 i)) ∧
                  Function.Surjective ex ∧
                  (∀ v, ex v = 0 ↔ v ∈ P.range) ∧
                  (∀ (c : 𝓞 H.E) v,
                    Pts.hom (ex (rawCoefficientAction H.toHostRaw 1 c v)) =
                      Pts.hom (ex v) ≫
                        (coefficientSerreSchemeFullAction H.toHostRaw G hbar B hB 1 a).act c) ∧
                  ∀ z x, Pts.hom (ex (z • P x)) =
                    ofAffinePoint V ℂ ((pointCongr hVC).symm
                      (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C)
                        ((C.u : ℂ)⁻¹ * z))) ≫
                      (coefficientSerreSchemeTensor H.toHostRaw G hbar B hB 1 a).tmul
                        (coefficientTwistedOne H.toHostRaw B x) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  let hbar := nativeDyadicGeometricHost_bar_eq e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro τ₀
  let _ : Algebra (OK G) ℂ := (embed G (τ₀ : H.E →+* ℂ)).toAlgebra
  have hcompat : ∀ τ : cmTypeFinset H.toHostRaw,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ := by
    intro τ
    exact nativeDyadic_quadraticEmbeddings_eq e q d he hH τ τ₀
  obtain ⟨M, hM, W, w, C, hΔ, hhost, hw, hLie, hLB, hpol,
    hu, hC, hsurj, hker, -, -⟩ :=
    WeierstrassPolarizedSeed.exists_integral_polarized_seed_with_exact_period
      G (τ₀ : H.E →+* ℂ)
  let _ : NumberField M := hM
  let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
  refine ⟨M, hM, W, w, C, hΔ, hhost, hw, hLie, hLB, hpol, hu,
    hC, hsurj, hker, originZ_hasDerivAt _ C, ?_⟩
  obtain ⟨F, hF, hMF, V, hV, hVC, a, hnorm, hact⟩ :=
    exists_cm_scheme_order_action G (τ₀ : H.E →+* ℂ) C M W w hC hw
  let _ : NumberField F := hF
  let _ : V.IsElliptic := hV
  obtain ⟨hsmooth, hproper, hconn⟩ :=
    coefficientSerreScheme_geometricProperties H.toHostRaw G hbar B hB 1 V a
  obtain ⟨hNL, hNR⟩ :=
    coefficientSerreOriginBundle_isLB_and_rigidified H.toHostRaw G hbar B hB 1 V a
  refine ⟨F, hF, hMF, V, hV, hVC, a, hnorm, hact,
    hsmooth, hproper, hconn, hNL, hNR,
    coefficientSerreOriginBundle_symmetric H.toHostRaw G hbar B hB 1 V a, ?_, ?_⟩
  · rw [coefficient_complex_fibre_rank H.toHostRaw G hbar B hB]
    change Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).E / 2 = 2 * 2 ^ e
    rw [nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord]
    omega
  · exact ⟨purePeriodLinear H.toHostRaw G hcompat B 1,
      coefficientGenericPeriodExponential H.toHostRaw G hbar B hB τ₀ V C hVC a hact hcompat,
      purePeriodLinear_apply H.toHostRaw G hcompat B 1,
      coefficientGenericPeriodExponential_surjective
        H.toHostRaw G hbar B hB τ₀ V C hVC a hact hcompat,
      coefficientGenericPeriodExponential_ker
        H.toHostRaw G hbar B hB τ₀ V C hVC a hact hcompat,
      coefficientGenericPeriodExponential_coefficient
        H.toHostRaw G hbar B hB τ₀ V C hVC a hact hcompat,
      coefficientGenericPeriodExponential_period_smul
        H.toHostRaw G hbar B hB τ₀ V C hVC a hact hcompat⟩

end RHLean.Analysis.AlpogeThin

end
